package controller.utente;

import jakarta.servlet.ReadListener;
import jakarta.servlet.ServletInputStream;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.List;

import static org.mockito.Mockito.*;

class AggiornaCartServletTest {
    private AggiornaCartServlet servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private Carrello carrello;
    private RigaCarrello riga;
    private Libro libro;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servletUnderTest = new AggiornaCartServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        carrello = mock(Carrello.class);
        riga = mock(RigaCarrello.class);
        libro = mock(Libro.class);
    dispatcher = mock(RequestDispatcher.class);

        // mocks
        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("utente")).thenReturn(mock(Utente.class));
        // default tipo to avoid NPE in Validator
        when(((Utente) session.getAttribute("utente")).getTipo()).thenReturn("");
        when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
    }

    // helper to create a ServletInputStream from a string
    private ServletInputStream toServletInputStream(String str) {
        final InputStream byteStream = new ByteArrayInputStream(str.getBytes(StandardCharsets.UTF_8));
        return new ServletInputStream() {
            @Override
            public boolean isFinished() {
                try {
                    return byteStream.available() == 0;
                } catch (IOException e) {
                    return true;
                }
            }

            @Override
            public boolean isReady() {
                return true;
            }

            @Override
            public void setReadListener(ReadListener readListener) {
                // not needed for tests
            }

            @Override
            public int read() throws IOException {
                return byteStream.read();
            }
        };
    }

    @Test
    void testDoGet_UserIsAdmin() throws ServletException, IOException {
        Utente admin = mock(Utente.class);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(admin.getTipo()).thenReturn("Gestore");

        servletUnderTest.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_UpdateQuantitySuccess() throws ServletException, IOException {
        // setup user not admin
        Utente user = mock(Utente.class);
        when(session.getAttribute("utente")).thenReturn(user);
        when(user.getTipo()).thenReturn("user");

        // setup carrello with one riga
        when(carrello.getRigheCarrello()).thenReturn(List.of(riga));
        when(riga.getLibro()).thenReturn(libro);
        when(libro.getIsbn()).thenReturn("12345");

        // prepare JSON body {"isbn":"12345","quantity":2}
        String json = "{\"isbn\":\"12345\",\"quantity\":2}";
        when(request.getInputStream()).thenReturn(toServletInputStream(json));

        servletUnderTest.doGet(request, response);

        verify(riga).setQuantita(2);
        verify(session).setAttribute("carrello", carrello);
        verify(response).setStatus(HttpServletResponse.SC_OK);
    }

    @Test
    void testDoGet_ItemNotFound() throws ServletException, IOException {
        Utente user = mock(Utente.class);
        when(session.getAttribute("utente")).thenReturn(user);
        when(user.getTipo()).thenReturn("user");

        // carrello with a riga having different isbn
        when(carrello.getRigheCarrello()).thenReturn(List.of(riga));
        when(riga.getLibro()).thenReturn(libro);
        when(libro.getIsbn()).thenReturn("99999");

        String json = "{\"isbn\":\"12345\",\"quantity\":2}";
        when(request.getInputStream()).thenReturn(toServletInputStream(json));

        servletUnderTest.doGet(request, response);

        verify(response).sendError(eq(HttpServletResponse.SC_BAD_REQUEST), anyString());
    }
}
