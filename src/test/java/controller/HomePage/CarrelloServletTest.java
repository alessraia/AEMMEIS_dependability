package controller.HomePage;

import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletConfig;
import jakarta.servlet.ServletContext;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.util.ArrayList;
import java.util.List;

import static org.mockito.Mockito.*;

public class CarrelloServletTest {

    private CarrelloServlet servlet;
    private ServletConfig servletConfig;
    private ServletContext servletContext;

    @BeforeEach
    public void setUp() throws Exception {
        servlet = new CarrelloServlet();
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
        admin.setTipo("GestoreOrdini");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(adminDispatcher);

        servlet.doGet(request, response);

        verify(adminDispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenCarrelloHasNoAvailableBooks_setDisponibileNo() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");

        Libro libro1 = new Libro();
        libro1.setIsbn("111-AAA");
        libro1.setDisponibile(false);

        Libro libro2 = new Libro();
        libro2.setIsbn("222-BBB");
        libro2.setDisponibile(false);

        RigaCarrello riga1 = new RigaCarrello();
        riga1.setLibro(libro1);
        riga1.setQuantita(1);

        RigaCarrello riga2 = new RigaCarrello();
        riga2.setLibro(libro2);
        riga2.setQuantita(2);

        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga1);
        righe.add(riga2);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(righe);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getRequestDispatcher("/WEB-INF/results/stampaCarrello.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("disponibile", "no");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenCarrelloHasAvailableBooks_setDisponibileSi() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");

        Libro libro1 = new Libro();
        libro1.setIsbn("111-AAA");
        libro1.setDisponibile(false);

        Libro libro2 = new Libro();
        libro2.setIsbn("222-BBB");
        libro2.setDisponibile(true);

        RigaCarrello riga1 = new RigaCarrello();
        riga1.setLibro(libro1);
        riga1.setQuantita(1);

        RigaCarrello riga2 = new RigaCarrello();
        riga2.setLibro(libro2);
        riga2.setQuantita(2);

        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga1);
        righe.add(riga2);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(righe);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getRequestDispatcher("/WEB-INF/results/stampaCarrello.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("disponibile", "si");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenCarrelloIsEmpty_setDisponibileNo() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");

        List<RigaCarrello> righe = new ArrayList<>();

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(righe);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getRequestDispatcher("/WEB-INF/results/stampaCarrello.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("disponibile", "no");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenFirstBookIsAvailable_breaksLoopEarly() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");

        Libro libro1 = new Libro();
        libro1.setIsbn("111-AAA");
        libro1.setDisponibile(true); // First book is available

        Libro libro2 = new Libro();
        libro2.setIsbn("222-BBB");
        libro2.setDisponibile(false);

        RigaCarrello riga1 = new RigaCarrello();
        riga1.setLibro(libro1);
        riga1.setQuantita(1);

        RigaCarrello riga2 = new RigaCarrello();
        riga2.setLibro(libro2);
        riga2.setQuantita(2);

        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga1);
        righe.add(riga2);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(righe);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getRequestDispatcher("/WEB-INF/results/stampaCarrello.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("disponibile", "si");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenUserIsNull_processesCartNormally() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Libro libro1 = new Libro();
        libro1.setIsbn("111-AAA");
        libro1.setDisponibile(true);

        RigaCarrello riga1 = new RigaCarrello();
        riga1.setLibro(libro1);
        riga1.setQuantita(1);

        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga1);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(righe);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(null);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getRequestDispatcher("/WEB-INF/results/stampaCarrello.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("disponibile", "si");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenAllBooksAvailable_setDisponibileSi() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");

        Libro libro1 = new Libro();
        libro1.setIsbn("111-AAA");
        libro1.setDisponibile(true);

        Libro libro2 = new Libro();
        libro2.setIsbn("222-BBB");
        libro2.setDisponibile(true);

        Libro libro3 = new Libro();
        libro3.setIsbn("333-CCC");
        libro3.setDisponibile(true);

        RigaCarrello riga1 = new RigaCarrello();
        riga1.setLibro(libro1);

        RigaCarrello riga2 = new RigaCarrello();
        riga2.setLibro(libro2);

        RigaCarrello riga3 = new RigaCarrello();
        riga3.setLibro(libro3);

        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga1);
        righe.add(riga2);
        righe.add(riga3);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(righe);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getRequestDispatcher("/WEB-INF/results/stampaCarrello.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("disponibile", "si");
        verify(dispatcher, times(1)).forward(request, response);
    }
}
