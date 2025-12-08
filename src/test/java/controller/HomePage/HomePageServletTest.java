package controller.HomePage;

import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;
import org.mockito.ArgumentCaptor;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletConfig;
import jakarta.servlet.ServletContext;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.Mockito.*;
import static org.mockito.ArgumentMatchers.*;
import static org.junit.jupiter.api.Assertions.*;

public class HomePageServletTest {

    private HomePageServlet servlet;
    private ServletConfig servletConfig;
    private ServletContext servletContext;

    @BeforeEach
    public void setUp() throws Exception {
        servlet = new HomePageServlet();
        servletConfig = mock(ServletConfig.class);
        servletContext = mock(ServletContext.class);
        when(servletConfig.getServletContext()).thenReturn(servletContext);
        servlet.init(servletConfig);
    }

    @Test
    public void whenUserIsAdmin_forwardToAdminHomepage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher adminDispatcher = mock(RequestDispatcher.class);

        Utente admin = new Utente();
        admin.setTipo("GestoreProdotti");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(null);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(adminDispatcher);

        servlet.doGet(request, response);

        verify(adminDispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenCarrelloIsNull_createsNewCarrello() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Reparto repartoTendenza = new Reparto();
        repartoTendenza.setNome("Libri di Tendenza");
        List<Libro> libriHome = new ArrayList<>();
        Libro libro1 = new Libro();
        libro1.setTitolo("Test Book");
        libriHome.add(libro1);
        repartoTendenza.setLibri(libriHome);

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(repartoTendenza);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(null);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getAttribute("libriHome")).thenReturn(null);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getRequestDispatcher("/WEB-INF/results/homepage.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        // Capture the Carrello argument passed to session.setAttribute
        ArgumentCaptor<Carrello> carCaptor = ArgumentCaptor.forClass(Carrello.class);
        verify(session).setAttribute(eq("carrello"), carCaptor.capture());
        
        // Verify that the captured Carrello has its righeCarrello initialized
        Carrello capturedCarrello = carCaptor.getValue();
        assertNotNull(capturedCarrello.getRigheCarrello(), "RigheCarrello should be initialized");
        assertTrue(capturedCarrello.getRigheCarrello().isEmpty(), "RigheCarrello should be an empty list");
        
        verify(request).setAttribute("libriHome", libriHome);
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenCarrelloExists_doesNotCreateNew() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Carrello existingCarrello = new Carrello();
        existingCarrello.setRigheCarrello(new ArrayList<>());

        Reparto repartoTendenza = new Reparto();
        repartoTendenza.setNome("Libri di Tendenza");
        List<Libro> libriHome = new ArrayList<>();
        repartoTendenza.setLibri(libriHome);

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(repartoTendenza);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(existingCarrello);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getAttribute("libriHome")).thenReturn(null);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getRequestDispatcher("/WEB-INF/results/homepage.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(session, never()).setAttribute(eq("carrello"), any(Carrello.class));
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenRepartiInContext_usesContextReparti() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(new ArrayList<>());

        Reparto repartoTendenza = new Reparto();
        repartoTendenza.setNome("Libri di Tendenza");
        Libro libro1 = new Libro();
        libro1.setTitolo("Trending Book");
        List<Libro> libriHome = new ArrayList<>();
        libriHome.add(libro1);
        repartoTendenza.setLibri(libriHome);

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(repartoTendenza);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getAttribute("libriHome")).thenReturn(null);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getRequestDispatcher("/WEB-INF/results/homepage.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("libriHome", libriHome);
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenRepartiNotInContext_loadsFromDatabase() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(new ArrayList<>());

        Reparto repartoTendenza = new Reparto();
        repartoTendenza.setNome("Libri di Tendenza");
        List<Libro> libriHome = new ArrayList<>();
        repartoTendenza.setLibri(libriHome);

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(repartoTendenza);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getAttribute("libriHome")).thenReturn(null);
        when(servletContext.getAttribute("reparti")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/homepage.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<RepartoDAO> mocked = mockConstruction(RepartoDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(reparti))) {

            servlet.doGet(request, response);

            verify(servletContext).setAttribute("reparti", reparti);
            verify(request).setAttribute("libriHome", libriHome);
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void whenLibriHomeAlreadySet_doesNotReload() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Carrello carrello = new Carrello();
        List<Libro> existingLibri = new ArrayList<>();

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getAttribute("libriHome")).thenReturn(existingLibri);
        when(request.getRequestDispatcher("/WEB-INF/results/homepage.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(servletContext, never()).getAttribute("reparti");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenMultipleReparti_findsLibriDiTendenza() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Carrello carrello = new Carrello();

        Reparto reparto1 = new Reparto();
        reparto1.setNome("Narrativa");
        reparto1.setLibri(new ArrayList<>());

        Reparto repartoTendenza = new Reparto();
        repartoTendenza.setNome("Libri di Tendenza");
        Libro libro1 = new Libro();
        libro1.setTitolo("Trending 1");
        Libro libro2 = new Libro();
        libro2.setTitolo("Trending 2");
        List<Libro> libriTendenza = new ArrayList<>();
        libriTendenza.add(libro1);
        libriTendenza.add(libro2);
        repartoTendenza.setLibri(libriTendenza);

        Reparto reparto3 = new Reparto();
        reparto3.setNome("Fumetti");
        reparto3.setLibri(new ArrayList<>());

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(reparto1);
        reparti.add(repartoTendenza);
        reparti.add(reparto3);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getAttribute("libriHome")).thenReturn(null);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getRequestDispatcher("/WEB-INF/results/homepage.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("libriHome", libriTendenza);
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenRegularUser_forwardsToHomepage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente regularUser = new Utente();
        regularUser.setTipo("Cliente");

        Carrello carrello = new Carrello();

        Reparto repartoTendenza = new Reparto();
        repartoTendenza.setNome("Libri di Tendenza");
        repartoTendenza.setLibri(new ArrayList<>());

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(repartoTendenza);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("utente")).thenReturn(regularUser);
        when(request.getAttribute("libriHome")).thenReturn(null);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getRequestDispatcher("/WEB-INF/results/homepage.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher, times(1)).forward(request, response);
        verify(request, never()).getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
    }

    @Test
    public void whenAdminDispatcherThrowsServletException_logsError() throws Exception {
        HomePageServlet spyServlet = spy(servlet);
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher adminDispatcher = mock(RequestDispatcher.class);

        Utente admin = new Utente();
        admin.setTipo("GestoreProdotti");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(null);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(adminDispatcher);
        doThrow(new ServletException("Test exception")).when(adminDispatcher).forward(request, response);

        spyServlet.doGet(request, response);

        verify(adminDispatcher, times(1)).forward(request, response);
        verify(spyServlet).log(contains("Errore durante il forward verso /WEB-INF/results/admin/homepageAdmin.jsp"), any(ServletException.class));
    }

    @Test
    public void whenAdminDispatcherThrowsIOException_logsError() throws Exception {
        HomePageServlet spyServlet = spy(servlet);
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher adminDispatcher = mock(RequestDispatcher.class);

        Utente admin = new Utente();
        admin.setTipo("GestoreProdotti");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(null);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(adminDispatcher);
        doThrow(new IOException("Test IO exception")).when(adminDispatcher).forward(request, response);

        spyServlet.doGet(request, response);

        verify(adminDispatcher, times(1)).forward(request, response);
        verify(spyServlet).log(contains("Errore di I/O durante il forward verso /WEB-INF/results/admin/homepageAdmin.jsp"), any(IOException.class));
    }

    @Test
    public void whenHomepageDispatcherThrowsServletException_logsError() throws Exception {
        HomePageServlet spyServlet = spy(servlet);
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Reparto repartoTendenza = new Reparto();
        repartoTendenza.setNome("Libri di Tendenza");
        List<Libro> libriHome = new ArrayList<>();
        repartoTendenza.setLibri(libriHome);

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(repartoTendenza);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(null);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getAttribute("libriHome")).thenReturn(null);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getRequestDispatcher("/WEB-INF/results/homepage.jsp")).thenReturn(dispatcher);
        doThrow(new ServletException("Test exception")).when(dispatcher).forward(request, response);

        spyServlet.doGet(request, response);

        verify(dispatcher, times(1)).forward(request, response);
        verify(spyServlet).log(contains("Errore durante il forward verso /WEB-INF/results/homepage.jsp"), any(ServletException.class));
    }

    @Test
    public void whenHomepageDispatcherThrowsIOException_logsError() throws Exception {
        HomePageServlet spyServlet = spy(servlet);
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Reparto repartoTendenza = new Reparto();
        repartoTendenza.setNome("Libri di Tendenza");
        List<Libro> libriHome = new ArrayList<>();
        repartoTendenza.setLibri(libriHome);

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(repartoTendenza);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(null);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getAttribute("libriHome")).thenReturn(null);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getRequestDispatcher("/WEB-INF/results/homepage.jsp")).thenReturn(dispatcher);
        doThrow(new IOException("Test IO exception")).when(dispatcher).forward(request, response);

        spyServlet.doGet(request, response);

        verify(dispatcher, times(1)).forward(request, response);
        verify(spyServlet).log(contains("Errore di I/O durante il forward verso /WEB-INF/results/homepage.jsp"), any(IOException.class));
    }
}
