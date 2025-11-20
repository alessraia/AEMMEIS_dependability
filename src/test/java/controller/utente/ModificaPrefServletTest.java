package controller.utente;

import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Reparto;
import model.utenteService.Utente;
import model.wishList.WishList;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletContext;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

public class ModificaPrefServletTest {

    @Test
    public void whenUserNull_forwardToLogin() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getParameter("isbn")).thenReturn("ISBN-1");
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        Libro libro = new Libro();
        libro.setIsbn("ISBN-1");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ISBN-1")).thenReturn(libro))) {

            new ModificaPrefServlet().doGet(request, response);

            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void addBookToEmptyWishList_bookAdded() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setEmail("user@test.com");

        WishList wishList = new WishList();
        wishList.setLibri(null); // empty wishlist

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(request.getParameter("isbn")).thenReturn("ISBN-2");
        when(request.getParameter("source")).thenReturn(null);
        when(request.getParameter("position")).thenReturn(null);
        when(request.getRequestDispatcher("index.html")).thenReturn(dispatcher);

        Libro libro = new Libro();
        libro.setIsbn("ISBN-2");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ISBN-2")).thenReturn(libro))) {

            new ModificaPrefServlet().doGet(request, response);

            assertNotNull(wishList.getLibri());
            assertEquals(1, wishList.getLibri().size());
            assertEquals(libro, wishList.getLibri().get(0));
            verify(session, times(1)).setAttribute("wishList", wishList);
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void addBookToWishListWithExistingBooks_bookAdded() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setEmail("user@test.com");

        Libro existingLibro = new Libro();
        existingLibro.setIsbn("ISBN-EXISTING");

        List<Libro> libri = new ArrayList<>();
        libri.add(existingLibro);

        WishList wishList = new WishList();
        wishList.setLibri(libri);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(request.getParameter("isbn")).thenReturn("ISBN-NEW");
        when(request.getParameter("source")).thenReturn(null);
        when(request.getParameter("position")).thenReturn(null);
        when(request.getRequestDispatcher("index.html")).thenReturn(dispatcher);

        Libro newLibro = new Libro();
        newLibro.setIsbn("ISBN-NEW");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ISBN-NEW")).thenReturn(newLibro))) {

            new ModificaPrefServlet().doGet(request, response);

            assertEquals(2, wishList.getLibri().size());
            assertTrue(wishList.getLibri().contains(newLibro));
            verify(session, times(1)).setAttribute("wishList", wishList);
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void removeExistingBookFromWishList_bookRemoved() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setEmail("user@test.com");

        Libro libroToRemove = new Libro();
        libroToRemove.setIsbn("ISBN-REMOVE");

        List<Libro> libri = new ArrayList<>();
        libri.add(libroToRemove);

        WishList wishList = new WishList();
        wishList.setLibri(libri);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(request.getParameter("isbn")).thenReturn("ISBN-REMOVE");
        when(request.getParameter("source")).thenReturn(null);
        when(request.getParameter("position")).thenReturn(null);
        when(request.getRequestDispatcher("index.html")).thenReturn(dispatcher);

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ISBN-REMOVE")).thenReturn(libroToRemove))) {

            new ModificaPrefServlet().doGet(request, response);

            assertEquals(0, wishList.getLibri().size());
            verify(session, times(1)).setAttribute("wishList", wishList);
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void sourceWishList_forwardsToShowWishList() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        WishList wishList = new WishList();
        wishList.setLibri(new ArrayList<>());

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(request.getParameter("isbn")).thenReturn("ISBN-3");
        when(request.getParameter("source")).thenReturn("wishList");
        when(request.getParameter("position")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/showWishList.jsp")).thenReturn(dispatcher);

        Libro libro = new Libro();
        libro.setIsbn("ISBN-3");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ISBN-3")).thenReturn(libro))) {

            new ModificaPrefServlet().doGet(request, response);

            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void sourceReparto_forwardsToRepartoJsp() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        ServletContext servletContext = mock(ServletContext.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);
        jakarta.servlet.ServletConfig servletConfig = mock(jakarta.servlet.ServletConfig.class);

        Utente user = new Utente();
        WishList wishList = new WishList();
        wishList.setLibri(new ArrayList<>());

        Reparto reparto = new Reparto();
        reparto.setIdReparto(5);
        reparto.setNome("Fiction");

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(reparto);

        ModificaPrefServlet servlet = new ModificaPrefServlet();
        
        when(request.getSession()).thenReturn(session);
        when(servletConfig.getServletContext()).thenReturn(servletContext);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(request.getParameter("isbn")).thenReturn("ISBN-4");
        when(request.getParameter("source")).thenReturn("reparto");
        when(request.getParameter("repartoAttuale")).thenReturn("5");
        when(request.getParameter("position")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/reparto.jsp")).thenReturn(dispatcher);

        Libro libro = new Libro();
        libro.setIsbn("ISBN-4");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context1) -> when(mock.doRetrieveById("ISBN-4")).thenReturn(libro))) {

            // Initialize servlet with ServletConfig
            servlet.init(servletConfig);

            servlet.doGet(request, response);

            verify(request, times(1)).setAttribute("reparto", reparto);
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void sourceMostraLibro_forwardsToMostraLibroWithAttribute() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        WishList wishList = new WishList();
        wishList.setLibri(new ArrayList<>());

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(request.getParameter("isbn")).thenReturn("ISBN-5");
        when(request.getParameter("source")).thenReturn("mostraLibro");
        when(request.getParameter("position")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/mostraLibro.jsp")).thenReturn(dispatcher);

        Libro libro = new Libro();
        libro.setIsbn("ISBN-5");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ISBN-5")).thenReturn(libro))) {

            new ModificaPrefServlet().doGet(request, response);

            verify(request, times(1)).setAttribute("libro", libro);
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void withPosition_appendsAnchorToAddress() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        WishList wishList = new WishList();
        wishList.setLibri(new ArrayList<>());

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(request.getParameter("isbn")).thenReturn("ISBN-6");
        when(request.getParameter("source")).thenReturn(null);
        when(request.getParameter("position")).thenReturn("top");
        when(request.getRequestDispatcher("index.html#top")).thenReturn(dispatcher);

        Libro libro = new Libro();
        libro.setIsbn("ISBN-6");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ISBN-6")).thenReturn(libro))) {

            new ModificaPrefServlet().doGet(request, response);

            verify(request, times(1)).getRequestDispatcher("index.html#top");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }
}
